# V7 selected Pool semantic-terminal source bridge

This bundle freezes the two production Tag-73 semantic roots used by the
eight-lane Pool at source revision
`68ac0c73a1f93cc42c81ea04df52cd26d80ec79c`:

- private transfer selected masked terminal;
- withdrawal selected masked terminal.

Both roots pass Charon, Aeneas, and Lean 4.31. The generated definitions are
transparent through the complete selected terminal implementation. The only
Charon opacity requested is `aspis_core::field::qm31_dot3`, whose arithmetic
is already covered by the focused field source bridge.

Charon embeds source text and nondeterministically allocated declaration IDs in
raw LLBC, so the replay does not mislabel that JSON as byte-reproducible. It
checks the exact roots/include/opacity profile and `has_errors=false`, then
requires Aeneas' generated Lean files to match the frozen files byte for byte.

The prior CU-lock bundle retained two selector helpers only as clean LLBC
because Aeneas could not join their borrowed mutable-slice control flow. The
production rewrites pinned here preserve the literal arithmetic while using
fixed arrays and explicit loops; Aeneas now translates the complete roots.

`V7SelectedSemanticRootBridge.lean` proves from the literal generated control
flow that successful private-transfer and withdrawal roots each require a
successful `terminal_parts` result. An inner semantic error cannot be converted
to an accepted field value. The exact `#print axioms` union is:

- `propext`
- `Classical.choice`
- `Quot.sound`

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, project axiom, or
opaque external model in the compiled bridge. The filled external files model
standard Rust iterator/array/bit operations transparently.

The final NUC replay completed Charon/Aeneas in 36.52 seconds at 745,788 KiB
peak RSS, and compiled every generated, external-model, and bridge Lean file in
23.71 seconds at 3,121,352 KiB peak RSS. Both runs used zero swap.

## Replay

On `nuc.local`, set the pinned binaries and run:

```bash
export CHARON_BIN=/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon
export AENEAS_BIN=/home/dombarker/project-offloads/v7-pure-debug-build-output-r2/aeneas-borrowfree-variantfn-namespace-r1
export RUSTUP_BIN=/home/dombarker/.cargo/bin/rustup
./aeneas-verif/v7-tag73-selected-pool-callers-current/replay-extraction-nuc.sh

export AENEAS_LEAN_BACKEND=/home/dombarker/project-offloads/aeneas-d860-v6-src/backends/lean
export LAKE_BIN=/home/dombarker/.elan/bin/lake
./aeneas-verif/v7-tag73-selected-pool-callers-current/replay-lean.sh
```

`verify-pins.sh` provides the quick source, artifact, selected-root, and
forbidden-construct audit without rebuilding the extraction.

The source-to-mathematics composition above `terminal_parts` remains the next
formal step. This bundle removes the mechanical source-translation obstruction;
it does not claim the unconditional K1.3--K1.6 probability capstone by itself.
