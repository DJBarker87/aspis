# Serialized replay environment record

## Rejected cached backend

The first packaged replay was invoked against
`<repo>/backends/lean`. All package, deployed-source,
and manifest checks passed. Compilation stopped at the first generated module,
before any bundle theorem was checked, with:

```text
TypesExternal.lean:2:0: error: failed to read file
Mathlib/Lean/Linter.olean, incompatible header
```

That rejected cached `Linter.olean` has SHA-256
`ee0dc759fab661a393748b69659b3af1aa42ab7c91d80e953415db3492471874`.
No dependency rebuild or broad Lake build was attempted.

## Accepted retry backend

The authorized single retry uses
`<local-tool>`, a byte-preserving filesystem
clone of the already-passing pinned d860 Aeneas Lean backend. It is outside any
ephemeral extraction directory.

| Item | Identity |
| --- | --- |
| Aeneas source revision represented by the backend | `d860ac47ed548d3da6d799afc013779ce470516c` plus the pinned bundle patches |
| Lean | 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783` |
| `lake-manifest.json` SHA-256 | `7d527c1294d4a157d9b4266728124893d3324db4fee7b21a34f1595c7bc61de5` |
| `lean-toolchain` SHA-256 | `efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee` |
| `Aeneas.olean` SHA-256 | `b5c7a91a3702ebada269660ee46c0c4db57e04db885bdece4d0e32f34a3ea42e` |
| accepted cache `Mathlib/Lean/Linter.olean` SHA-256 | `68adcc26a81eb2d90c73e276addd348783116a39f154f7e4703ada918bdc0057` |

The backend is the pinned dependency base for the focused integrated replay.
The replay remains `LEAN_NUM_THREADS=1`; it does not run a broad Lake build or
repository regression suite. In dependency order it stages and compiles only:

1. the packaged four-root Merkle generated modules;
2. the source-pinned deferred-parser generated modules and parser source
   bridge;
3. the frozen query grammar, extractor, and parser-roundtrip modules;
4. the source, layout, accepted, traversal, inner-trace, and outer-trace
   bridges;
5. the result-aware caller generated modules and namespace bridge; and
6. `V7MerkleK12CallerBridge.lean`, including
   `translated_caller_success_implies_accepted_two_tree_openings` and its
   `#print axioms` command.

## NUC memory and serialization policy

Any Charon/Aeneas regeneration or genuinely memory-intensive Lean replay must
run on the dedicated Linux build host. Immediately before launch, `/proc/meminfo` must report
`MemAvailable >= 25165824 kB` (24 GiB). The workload must use the established
cgroup limits:

```text
MemoryHigh=22G
MemoryMax=28G
MemorySwapMax=0
```

Heavy jobs are serialized. No replay may kill, pause, reprioritize, or
otherwise interfere with unrelated NUC processes. Each final run records the
exact command, wall time, user/system time, maximum RSS or cgroup peak, swap,
exit status, cgroup identity, and MemAvailable gate.

The standalone caller namespace bridge passed under this policy with exit 0 in
23.69 seconds,
2,612,928 KiB maximum RSS, and zero swaps.

The complete serialized parser-through-caller replay passed with exit 0 in
1:46.57, at 7,097,940 KiB maximum RSS and zero swaps. `REPLAY-RESULT.txt`
contains the resource record, and `evidence/full-replay-candidate-04/axioms.txt`
contains the complete 118-entry axiom output.
