# Frozen extraction commands

Tool versions:

- Charon `0.1.223`, Linux binary from the pinned Aspis formal toolchain.
- Aeneas commit/binary `d860`, Lean backend, split files.

The LLBC headers record all Charon options and source contents.  The focused
roots were extracted with the Aeneas preset and `--sysroot default`:

```text
aspis_pool::pair_forest_dispatch::invoke_pair_forest_terminal_with_runtime_v1
  include: aspis_statement::pool_v1::pair_forest_terminal
  output: ASQ8Dispatch.llbc

aspis_pool::pair_forest::next_pair_forest_lane_v1
  output: ASQ8NextLane.llbc

aspis_pool::pair_forest::process_pair_forest_terminal_with_verifier_v1
  output: ASQ8CallerRaw.llbc
```

Focused Aeneas translation shape:

```sh
aeneas -backend lean -namespace ASQ8Dispatch -dest <dir> -split-files \
  -abort-on-error ASQ8Dispatch.llbc
aeneas -backend lean -namespace ASQ8NextLane -dest <dir> -split-files \
  -abort-on-error ASQ8NextLane.llbc
```

The generated files committed here additionally apply only the documented
module-prefix, discriminant, constant-arithmetic, and transparent-external
normalizations in `source-transform/README.md`.
