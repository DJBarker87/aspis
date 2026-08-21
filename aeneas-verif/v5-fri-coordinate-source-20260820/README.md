# V5 FRI coordinate source model

This bundle records the complete Charon/Aeneas model of the coordinate and
batch-inverse calculation used by the released V5 FRI check. The generated
Lean body contains no `sorry`.

The pinned Aeneas release could not translate three Rust surface forms in the
unchanged helper: a function-pointer argument, iterator `try_fold`, and a
mutable `array::from_fn` closure. `extraction-adapter.patch` specializes the
call to the released domain (`19`) and the actual inverse backend (`M31::inv`),
then spells those iterator operations as equivalent `while` loops. It does not
change the field formulas, routing, denominator order, batch inversion, or
returned coordinate layout. The patch is an extraction adapter, not a change
to the deployed program.

`aeneas-function-pointer-types.patch` records the small Aeneas type-translation
extension used while isolating the unsupported source forms. The final adapter
does not dynamically invoke a Rust function pointer.

The generated model has only four filled external definitions:

- `usize::reverse_bits` is the corresponding fixed-width bit-vector reverse;
- `slice::first` is `List.head?`;
- `Vec::is_empty` is list emptiness;
- `CIRCLE_LOG_ORDER` is the source constant `31`.

`FunsCombined.lean` is the byte-for-byte Aeneas output.  The replay compiles a
deterministic low-memory split of that same declaration stream.  The field
helpers, high window, low window, point helpers, and coordinate driver are
separate modules, in their original order.  Splitting prevents Lean from
retaining both large literal arrays and the expanded driver expression in one
elaboration process; it does not alter any definition.

The replay checks the handwritten proof modules which follow the translated
program from its field operations to its returned value:

- `V5FriCoordinateTableSemantics.lean` checks every one of the 256 low-window
  and 512 high-window literal points and relates them to the deployed
  generator;
- `V5FriCoordinateMathematics.lean` proves split-window reconstruction and
  the exact slot normalization performed at each of the three parent layers;
- `V5FriBatchInverseMathematics.lean` proves the batch-inversion mathematics;
- the field, denominator, inverse, point, and output-loop files prove each
  translated loop preserves the required value and order; and
- `V5FriCoordinateTopLevel.lean` and
  `V5FriCoordinateReleasedPointConnection.lean` prove that a successful
  adapter call returns the released circle, line, and final-coordinate tables
  for the supplied query indices.

This closes extraction of the coordinate algorithm itself.  There are now two
additional checks on the connection to the unchanged production source:

- Charon 0.1.223 and unmodified Aeneas `d860ac47` directly translate the
  private `derive_parent_line_points` helper.  The generated Lean in
  `generated/ParentCore/` compiles without an axiom or proof shortcut.
- the released domain-19 point shapes and all 18 released query ordinals are
  checked against the unchanged source by the recorded Kani harness.

The complete public coordinate driver still contains a mutable
`core::array::from_fn` closure that this Aeneas version cannot translate.  For
that reason the final equality is recorded only for the successful coordinate
call contained in an accepted production execution.  It is an explicit
source-tool certificate, not a Lean-kernel theorem and not a cryptographic
assumption.  Nothing in the proof assumes equality for arbitrary rejected
calls.

## Direct unchanged helper replay

`parent-helper-harness/Cargo.toml` points at the unchanged production
`aspis-core` source while giving Charon a standalone package name. Starting
from
`aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points`
produces helper-only LLBC. Charon's JSON includes the chosen output path and
unordered internal maps, so the replay pins the stable generated Lean files
rather than pretending the raw LLBC bytes are reproducible across runs.

The extraction uses:

```sh
charon cargo --preset aeneas \
  --start-from \
  aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points \
  --dest-file ParentCore.llbc -- --manifest-path \
  parent-helper-harness/Cargo.toml

aeneas -backend lean -split-files \
  -namespace V5FriCoordinateProduction \
  -dest generated -subdir ParentCore ParentCore.llbc
```

Run `replay-parent-helper-lean432.sh` with `AENEAS_LEAN_PATH` set to the full
Lean path printed by the matching Aeneas `lake env printenv LEAN_PATH`.  It
checks the source identity, generated-file identities, absence of proof holes,
and Lean 4.32 compilation.

With the pinned Charon and Aeneas executables also available,
`reextract-parent-helper.sh` reruns the extraction, checks that the normalized
generated definitions match the checked files, and then runs that Lean replay.

Pinned inputs:

- repository commit before this bundle: `b502a1e76dd6d03eff27e4f6d086a8b14d548f4c`;
- `circle_fri.rs` blob: `d9382a35ec7a660b696171e7609f443995a009bf`;
- `circle_openings.rs` blob: `2e4a07db0985b3c9db631616dedf590db5e78bd1`;
- Charon commit: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`;
- Aeneas base commit for the coordinate adapter:
  `9067e42e92bd8882f07dff2f72a61f16a01134af`;
- unmodified Aeneas commit for the direct parent-helper extraction:
  `d860ac47ed548d3da6d799afc013779ce470516c`;
- extracted LLBC SHA-256: `16742974b58908aa6bfba3f06a9ee349811705ef4ac54349b41207de5b9937c9`.

Run `replay-lean432.sh` with `AENEAS_LEAN_LIB` set to the Lean 4.32 Aeneas
library and `V5_FRI_ARITHMETIC_LEAN_OUT` set to the checked FRI arithmetic
output directory.  The replay compiles the complete coordinate proof and
scans it for proof shortcuts.
