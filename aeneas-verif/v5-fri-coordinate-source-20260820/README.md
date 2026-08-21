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

This closes extraction of the coordinate algorithm itself. Equality between
the extraction adapter and the unchanged Rust helper remains a toolchain
obligation until its separate Kani/differential proof is recorded; it is not a
cryptographic assumption and must not be presented as a Lean theorem about the
unchanged helper.

Pinned inputs:

- repository commit before this bundle: `b502a1e76dd6d03eff27e4f6d086a8b14d548f4c`;
- `circle_fri.rs` blob: `d9382a35ec7a660b696171e7609f443995a009bf`;
- `circle_openings.rs` blob: `2e4a07db0985b3c9db631616dedf590db5e78bd1`;
- Charon commit: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`;
- Aeneas base commit: `9067e42e92bd8882f07dff2f72a61f16a01134af`;
- extracted LLBC SHA-256: `16742974b58908aa6bfba3f06a9ee349811705ef4ac54349b41207de5b9937c9`.

Run `replay-lean432.sh` with `AENEAS_LEAN_LIB` set to the Lean 4.32 Aeneas
library and `V5_FRI_ARITHMETIC_LEAN_OUT` set to the checked FRI arithmetic
output directory.  The replay compiles the complete coordinate proof and
scans it for proof shortcuts.
