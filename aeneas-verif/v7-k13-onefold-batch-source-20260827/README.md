# V7 Tag-73 one-fold/query-batch source bridge

This focused bundle translates three literal production functions from
`aspis-core` at base commit
`b44fc616098b3018e098572885a688a5935e5b47`:

- `aspis_core::v6_onefold::fold_v6_onefold_queries`;
- `aspis_core::v6_query_batch::v7_final256_query_batch_shifted_residual`;
- `aspis_core::v6_query_batch::add_v7_final256_query_batch_shifted`, including
  its private shared helper.

Charon 0.1.223 follows both call graphs together.  Aeneas b59d518 translates
all M31/CM31/QM31 arithmetic in those graphs transparently.  The only external
operation is `core::array::from_fn`; `FunsExternal.lean` gives its exact
fixed-length-16 execution and fails closed at every other length.

`V7K13FoldedValuesTrace.lean` proves that a successful translated production
fold exposes the same preparatory alpha arithmetic and the exact ordered
array of sixteen callback results.  It intentionally proves no comparison
with `final256`: the deployed verifier does not perform sixteen pointwise
checks.

The companion main-project leaf
`AspisFormal/K1/V7Tag73BatchedQuerySourceBridge.lean` corrects the downstream
handoff.  Its source record states only the exact final256 covector and the
shifted rho-weighted claim of the authenticated array.
`QueryInjectionExact` follows only from an explicit equality supplied by the
joint discrepancy proof.

## Important protocol fact

The production Tag-73 verifier squeezes nonzero rho after selecting the
accepted q16 branch, calls the authenticated one-fold callback, and installs

```text
sum_{i=0}^{15} rho^(i+1) * authenticated[i].
```

It never calls `v7_final256_query_batch_shifted_residual`; that function is the
exact executable specification used by tests and by this bridge.  The expected
`final256` values enter through the line-evaluation weight covector and the
later relation terminal.  Consequently, accepted source alone does not imply
pointwise `IdealAccepts` or a standalone residual-zero fact.  The joint
pre-query/query discrepancy and its degree-16 collision event own that step.

The literal `finish_onefold_relation` order is:

1. finish final work and call the q16 scheduler;
2. replace the transcript by the selected accepted q16 branch;
3. check both frontier counts;
4. absorb the Tag-73 query-challenge label and squeeze nonzero rho;
5. call the authenticated one-fold callback;
6. call the shifted Tag-73 batch helper and absorb its returned claim.

`finish_v7_compact_relation` passes the shifted-batch switch as `true`.
`finish_v6_relation` passes it as `false` and therefore retains the frozen
start-at-one V6 helper.

## Extraction-only scale-loop normalization

Direct Charon extraction of `add_v7_final256_query_batch_shifted` succeeds,
but Aeneas b59d518 aborts at the shared scale-building loop in
`InterpJoin.ml` with `Could not match the contexts`.  The replay therefore
applies one hash-pinned extraction-only normalization: it expands the fixed
fifteen-step prepared-multiplication recurrence into scalar locals and builds
the same length-16 scale array as one literal.  Query validation, the
`add_line_m31_batch` call, `qm31_dot`, the running-claim update and all result
flow remain byte-identical around that block.  Charon/Aeneas then translate
the whole function transparently.

A second hash-pinned generated-code compatibility patch removes two
`Iterator::any` record-field assignments that Aeneas b59d518 emits for the
current Rust library although the pinned Aeneas Lean backend predates that
trait field.  The literal `any` call remains in the generated function and is
implemented transparently in `FunsExternal.lean`; no program behavior is
removed or made opaque.

`V7K13QueryBatchInsertionTrace.lean` starts from successful execution of that
translation and exposes the exact sixteen scales, exact line-covector
insertion call, exact authenticated-value dot product and exact running-claim
addition.  All Rust-library iterator/sort operations have executable Lean
models; no protocol conclusion is placed behind an opaque interface.

No production Rust is changed by this bundle.

## Prover/verifier routing and compatibility audit

The verifier's `finish_v7_compact_relation` passes the Tag-73 shifted switch
to `finish_onefold_relation`, which dispatches to
`add_v7_final256_query_batch_shifted`.  `finish_v6_relation` passes the frozen
V6 switch and dispatches to `add_v6_final256_query_batch`.  The prover mirrors
this split in `build_onefold_proof`: only `OneFoldBuildProfile::V7Compact`
uses the shifted helper; `OneFoldBuildProfile::V6` remains start-at-one.

The repair changes no proof field, byte offset, proof length, transcript label,
query schedule, Merkle frontier, or work bits.  It changes the Tag-73 query
claim absorbed into the transcript and therefore its three later relation
messages.  Existing Tag-73 proofs, hashes, release binaries, CU evidence and
devnet lifecycle records must be regenerated; Tag-72/V6 artifacts remain
compatible.

There is no arithmetic CU increase in the shifted batch itself: both helpers
construct one prepared-rho multiplier and perform the same fifteen prepared
multiplications, line-covector insertion, dot product and claim addition.  The
only new control-flow cost is the Tag-73/V6 helper selection in the shared
relation path.  That delta is expected to be negligible but is deliberately
left as an empirical release measurement rather than asserted as an exact CU
number here.
