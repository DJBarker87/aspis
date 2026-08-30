# V7 Tag-73 K1.2 literal-source integration

Date: 2026-08-28

Branch base: `b76fee418079aaa244cbca4b3ffb26d8a4808192`

Imported caller/source bridge ancestor:
`9d77e385504370ba763867985e65f12ce1cdbc47`

## Result

The principal theorem is:

```text
literal_production_callers_construct_exact_tag73_k12_source_obligations
```

It constructs the maintained `ExactTag73K12SourceObligations` for every
accepted exact operational input.  Both fields are proved:

- `openingsAccepted`: the literal translated caller's two shared-topology
  trees authenticate the 16 paired openings against the exact maintained C1
  and C2 roots; and
- `suppliedCovered`: every leaf and node input used by those openings occurs
  in the exact verifier-final shared-oracle history, hence
  `ExactPrefixK12SuppliedCoverage` holds.

The construction starts from the Aeneas-translated production caller call

```text
verify_and_gamma_combine_v7_openings ... = .ok (.Ok output)
```

and uses the existing exact caller-control-flow bridge.  It reconstructs the
actual selected opening batch, proves its roots and opening records equal the
maintained post-parser projections, derives each fold/root equality, derives
the two per-tree `TraceIncludedInLog` predicates, and finally constructs both
K1.2 source-obligation fields.  Neither `accepted_two_tree_openings`,
`TraceIncludedInLog`, `ExactPrefixK12SuppliedCoverage`, extraction success,
nor a K1.2 error/probability conclusion is assumed.

## Exact remaining runtime/tool boundary

The generated Aeneas `GeneratedHash` callback is a pure Lean function.  It
records its digest result but has no effectful oracle-table or ordered-history
state.  The maintained exact plain-ROM execution owns that history separately.
Consequently the translated caller theorem alone cannot prove that a source
callback invocation was inserted into that separately modeled final history.

`SourceOpeningRuntimeReflection` is the isolated boundary.  For each of the
16 literal source openings it states only:

- the C1 and C2 leaf callback results equal the maintained 208-bit truncation;
- the exact serialized C1 and C2 leaf inputs occur in the final history; and
- recursively for every literal left/right node call, its returned 208-bit
  digest equals the maintained truncation and its exact ordered node input
  occurs in the final history.

This is the only runtime/effect semantic boundary.  It is a per-call
callback-to-shared-history reflection capability, strictly below the K1.2
conclusion, and contains no whole-trace coverage or acceptance field.  Removing
it requires an effectful source/runtime model that threads the same oracle
state through the translated SHA callback; the current pure Aeneas callback
cannot express that fact.

The binding also states the transparent structural equalities that the
generated wire roots and reconstructed opening batch are the exact maintained
post-parser roots/openings.  Those are source-to-model value projections, not
Merkle acceptance or coverage conclusions.  Eliminating them would require
making the maintained operational input carry the literal translated wire
identity rather than only its post-parser projections.

## Compatibility proof change

`V7Tag73ReplayWorkEvidenceBridge.lean` no longer uses Lean 4.32's
`List.find?_congr`.  A direct list induction proves the same selector equality.
This lets the maintained exact K1.2 definitions compile under the caller
bundle's pinned Lean 4.31 toolchain without changing any theorem statement.
The same file also passed its native Lean 4.32 target build.

## Focused replay evidence

The clean source/integration replay ran on the dedicated Linux build host under:

```text
MemoryHigh=22G
MemoryMax=28G
MemorySwapMax=0
LEAN_NUM_THREADS=1
```

| Target | Result | Wall | Maximum RSS | Process swaps |
|---|---:|---:|---:|---:|
| Clean generated/parser/caller/integration replay, Lean 4.31 | PASS | 1:43.84 | 6,957,656 KiB | 0 |
| Maintained compatibility target, native Lean 4.32 | PASS | 1:53.16 | 6,822,924 KiB | 0 |

The clean replay unit was
`aspis-v7-k12-source-integration-final-01`, invocation
`4fc7830d823547368d3abbbf5878a895`.  It rechecked the frozen generated/caller
manifests before compiling the exact source bridges and the integration
theorem.  The native focused unit was
`aspis-v7-k12-source-native-03`, invocation
`634a0e779d65417cba399af11a182ddc`.

Every printed integration theorem has the exact axiom union:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, explicit project
axiom, or conclusion-shaped K1.2 premise in the changed proof sources.

## Replay

The focused replay entry point is:

```text
aeneas-verif/v7-merkle-k12-accepted-source-20260825/
  replay-exact-k12-integration.sh
```

It is NUC-only, requires the exact maintained K1.2 olean root, verifies the
frozen bundle manifests, enforces the 22/28 GiB zero-swap cgroup, compiles with
one Lean thread, and deletes only its guarded task-specific temporary replay
directory.
