# Direct Rust proof for the released circle-point helper

This bundle proves the released `domain_log_size = 19` path of the unchanged
production Rust function `selected_circle_fiber_points_shared`.

The proof starts from the function produced by Charon and Aeneas. It proves
that, when every input fibre is below `2^17`, the public Rust helper succeeds,
returns one point per input, preserves input order, and returns exactly the
circle point used by the maintained FRI mathematics.

The main theorem is:

```text
V5CoordinateSelectedProductionProof.
  source_selected_circle_fiber_points_shared_domain19_exact
```

The supporting loop theorem is:

```text
V5CoordinateSelectedProductionProof.source_selected_points_loop_exact
```

No equality assumption is used for this helper. The proof files contain no
`sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or compiled-evaluation
shortcut. Lean reports only its ordinary logical foundations for the three
printed theorem checks.

## Translator correction

The Rust loop returns an owned `Vec`. Charon emits a `Drop` cleanup between
the write to the Rust return place and the loop exit. Aeneas already ignored
that `Drop` during ordinary interpretation, but its nested-return recovery
only skipped `StorageDead` and `Nop`. The mismatch translated normal loop
exhaustion as `None`, followed by a panic in the outer function.

`aeneas-drop-cleanup-return.patch` adds `Drop` to that cleanup scan only when
Aeneas is already running with `drop_as_no_op`. It is a three-line change.
After the change, the generated function has the intended branches:

- normal iterator exhaustion returns `Ok(points)`;
- an out-of-range fibre returns `CircleFiberOutOfRange`; and
- the public domain-19 branch returns the loop result directly.

The Lean loop and public-function theorems above are the semantic regression
check for the corrected translation, including normal exhaustion and all
successful iterations.

The production source identity checked by the replay is the Git blob
`d9382a35ec7a660b696171e7609f443995a009bf`. The translator base is Aeneas
`d860ac47ed548d3da6d799afc013779ce470516c`, with the recorded patch applied.

## What this closes

This removes the direct-source gap for production circle-point selection at
the released domain size. The old adapter proof is still used for the already
proved field and circle-table mathematics; this bundle proves that the actual
Rust loop returns those same points.

It does **not** yet remove the full coordinate-driver certificate
`AcceptedExecutionCoordinateSourceCertificate`. The complete production
function `derive_query_fold_inverses_for_circle` still has four translation
problems outside this helper:

1. the denominator-count closure's `FnOnce::call_once` reaches a slice
   projector case that Aeneas does not yet interpret;
2. the mutable closure used by `array::from_fn` fails while joining the
   closure state;
3. the `vec![M31::ZERO; len]` expansion reaches an unsupported borrow shape;
4. `Iterator::try_fold` and Rust's `Try` trait do not match the pinned Lean
   builtin description.

Until those four source constructs are translated and proved, the exact
remaining bridge names in the existing consumer proof are:

```text
AcceptedProductionCoordinateAdapterEquality
AcceptedExecutionCoordinateSourceCertificate
```

They are engineering/source-translation boundaries, not missing circle-code,
FRI-distance, or field-mathematics theorems.

## Replay

First replay the existing coordinate proof bundle and keep its output path.
Then run:

```sh
AENEAS_LEAN_PATH=/path/to/aeneas/lean/path \
V5_FRI_COORDINATE_REPLAY_OUT=/path/to/checked/coordinate/output \
V5_FRI_ARITHMETIC_LEAN_OUT=/path/to/checked/fri/arithmetic/output \
ASPIS_FORMAL_LEAN_PATH=/path/to/checked/AspisFormal/lean/output \
./replay-lean432.sh
```

The replay checks the production source blob, file hashes, forbidden proof
shortcuts, all focused generated modules, and the public theorem under Lean
4.32.
