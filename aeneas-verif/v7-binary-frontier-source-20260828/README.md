# V7 production binary-frontier source bridge

This bundle extracts the literal production
`aspis_core::v6_onefold::binary_frontier_nodes` implementation and proves both
the arithmetic performed by each adjacent-window body and the complete
translated windows loop.

The source tree used for the final caller extraction was based on
`8faea1a6578ea4c903fb7c145679780157dd8a21` on
`research/v7-q16-scheduler-replay-20260828`, with the control-flow-only caller
refactor recorded in the same checkpoint as this bundle.

## Extraction

The pinned Linux Charon command was:

```text
/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon cargo \
  --preset aeneas \
  --start-from crate::v6_onefold::binary_frontier_nodes \
  --dest-file frontier-extraction/V7BinaryFrontier.llbc \
  -- --manifest-path crates/aspis-core/Cargo.toml --lib
```

The pinned Aeneas command was:

```text
/home/dombarker/project-offloads/aeneas-d860-v6-linux/bin/aeneas \
  -backend lean -split-files -emit-json \
  -namespace V7BinaryFrontierSource \
  -dest frontier-extraction/generated \
  frontier-extraction/V7BinaryFrontier.llbc
```

The generated `*_Template.lean` files are not part of this bundle and are not
imported. `TypesExternal.lean` and `FunsExternal.lean` provide transparent
definitions for the small foreign iterator/option/shift surface used by the
extraction.

## Current strongest result

`V7BinaryFrontierLoopBridge.translated_windows_loop_exact` starts from the
literal translated iterator state, an exact duplicate-free remaining list and
the checked `usize` headroom. It constructs translated loop success and proves
that the final accumulator is:

```text
expanded + sum(floor(log2(left[i] XOR left[i + 1])))
```

Its body theorem follows the translated XOR, nonzero assertion,
`leading_zeros`, both checked `u32` subtractions, the `u32 -> usize` cast and
the checked `usize` addition. The loop theorem then follows every translated
`windows(2)` transition and checked addition. There is no arithmetic callback
or conclusion-shaped source premise.

The insertion-sort and fixed-q16 closures are source-backed:

- `V7BinaryFrontierSortModel.bubbleLeft_sorted_prefix` and
  `bubbleLeft_perm` prove the pure adjacent-swap insertion mathematics; and
- `V7BinaryFrontierSortSourceBridge.translated_inner_insertion_exact` proves
  that the literal translated predecessor-shift loop, followed by writing its
  saved key at the returned cursor, is exactly that `bubbleLeft` operation;
- `translated_outer_insertion_sort_exact` and `translated_sort_from_one`
  prove that production's complete outer loop returns a sorted permutation;
- `translated_duplicate_scan_accepts` proves literal adjacent duplicate
  validation accepts every pairwise-distinct sorted schedule; and
- `translated_binary_frontier_q16_exact` starts from the complete production
  helper at `q = 16`, depth 18 and proves its exact checked return formula.

`V7BinaryFrontierK13Integration.translated_frontier_nodes_eq_semantic` then
constructs the operational Rust `u32[16]` from the Tag-73 query injection and
proves that the translated helper returns exactly
`semanticFrontierNodes schedule.positions`. This discharges the former
pointwise frontier-mathematics input when the accepted tape is instantiated
with the production helper.

The enclosing production
`aspis_core::v7_onefold::derive_first_v7_compact_queries` caller has also been
extracted from the same source revision. Its generated helper namespace is
replayed independently through the body, loop, insertion-sort and K1.3
integration bridges under `caller/proof/`. In particular,
`V7FirstCompactFrontierK13Integration.translated_frontier_compact_iff_semantic`
proves that the literal helper's cap-203 decision is equivalent to the frozen
K1.3 semantic admission predicate.

`V7FirstCompactCallerBridge.source_candidate_reduces` now follows the complete
loop-free production candidate helper from transcript clone through query
sampling, exact `u32[16]` conversion, the source-backed frontier calculation
and its cap decision. Its two public consequences prove that a semantically
admitted candidate returns all five exact schedule fields and that a
non-admitted candidate returns `none`.

The reverse direction is now source-backed as well.
`candidate_success_exposes_raw_execution` inverts a literal successful
translated candidate call into its actual clone, one-byte counter absorb,
checked shift, sampler, `Vec -> u32[16]`, frontier and exact return stages.
`raw_execution_to_candidate_prefix` then reduces the K1.3 semantic handoff to
one narrow equality: the returned raw array is
`queryScheduleArray schedule`.  The checked shift result is proved internally
to be exactly `2^18` by `raw_candidate_bound_exact`.  In particular, the remaining
digest-block/decoder alignment no longer assumes the translated source control
flow, frontier result, or candidate return.

`V7FirstCompactK13RawScheduleBridge.raw_queries_eq_decoded_schedule` closes the
array/decoder half of that equality.  Given equality between the translated
sampler's ordered values and the existing deployed decoder's consumed-block
scan, it proves exact `u32[16]` array equality.  The complete wrapper theorem
`translated_wrapper_returns_first_semantic_candidate_of_raw_runs` therefore
needs no `CandidatePrefixRuns` inputs: literal candidate calls plus this ordered
sampler-value alignment determine every earlier rejection and the selected
five-field return.

The caller extraction required transparent generated-code repairs: avoid the
`transcript` parameter/name-space shadow, reuse the already generated frontier
types and foreign definitions, and supply the literal extra `u32`,
`Result.map_err`, and `Vec -> Array` operations. Production Rust received one
control-flow-only refactor: a loop-free candidate helper returns the same five
field schedule, while the outer loop records the first successful helper result
before breaking. The proof relation, transcript, cap, wire format and
cryptographic parameters are unchanged. A focused Rust test checks that the
outer API still selects the first admitted candidate.

## Replay

On `nuc.local`, with pinned Aeneas Lean backend and Lean 4.31:

```text
systemd-run --user --wait --collect \
  --unit=aspis-v7-frontier-loop-06 \
  -p MemoryHigh=22G -p MemoryMax=28G -p MemorySwapMax=0 \
  ./compile-generated.sh <generated-lean-root> \
  /home/dombarker/project-offloads/aeneas-d860-v6/backends/lean
```

Result: exit 0, 11.699 seconds service runtime, zero swap. `#print axioms`
reported exactly:

```text
propext
Classical.choice
Quot.sound
```

The focused sort-source replay used unit
`aspis-v7-frontier-sort-source-07`; it exited 0 in 14.692 seconds with zero
swap and reported the same exact axiom set.

The full fixed-q16 replay used unit
`aspis-v7-frontier-full-q16-final`; it exited 0 in 15.194 seconds with zero
swap. The K1.3 integration can be included by supplying a Lean-4.31
AspisFormal project containing the focused semantic frontier build:

```text
./compile-generated.sh <generated-lean-root> \
  /path/to/aeneas/backends/lean \
  /path/to/aspis-formal-project
```

The caller extraction, four caller frontier bridges and exact candidate-return
bridge were also compiled with the same Lean 4.31/AspisFormal path and zero
swap. The focused final candidate-return replay used unit
`aspis-v7-helper-caller-return-bridge-09`; it exited 0 in 3.797 seconds. GNU
`time -v` measured 6,806,380 KiB peak RSS and reported zero swaps.
The complete narrow bundle replay used unit
`aspis-v7-caller-helper-full-replay-01`; it exited 0 in 39.181 seconds, peaked
at 6,849,076 KiB RSS and reported zero swaps. Every printed theorem remained a
subset of `propext`, `Classical.choice` and `Quot.sound`.

The subsequent outer-loop closure used focused unit
`aspis-v7-first-success-loop-04`; it exited 0 in 3.731 seconds, peaked at
6,825,212 KiB RSS and reported zero swaps. Its strongest theorem,
`translated_wrapper_returns_first_semantic_candidate`, follows the literal
`u8` range iterator, rejects every preceding semantic non-candidate, selects
the first cap-203 candidate, and returns its exact five-field schedule through
the complete translated wrapper.
The final complete narrow replay used unit
`aspis-v7-caller-first-success-full-replay-02`; it exited 0 in 39.291 seconds,
peaked at 6,852,016 KiB RSS and reported zero swaps.

The focused raw schedule bridge replay used units
`aspis-v7-wrapper-raw-runs-03` and `aspis-v7-raw-schedule-bridge-04`; both
exited 0.  The latter took 3.84 seconds.  The matching deployed-decoder module
was built once in unit `aspis-v7-decoder-prefix-build-fast-01` (8,630 jobs,
1:17.75 wall, 7,102,848 KiB peak RSS, zero swaps).

## Digests

```text
166a91348ba468ddecd16574154b5425609276d51f7d3dfbfb07effce4d6a406  extraction/V7BinaryFrontier.llbc
1b9ba984d8238a7c5da264078f134c4c3f587a9c13bea7a7cfe74adad3c9a26e  generated/V7BinaryFrontier/Funs.lean
29b8692b94e73d1c0d59ab27dbdf5160e285636585add7dbadaba50f631a467f  proof/V7BinaryFrontierBodyBridge.lean
3911bf62d05373ce65cc2d0bcb0996dab4551445c76ca06e8e905c5e9c73e65a  proof/V7BinaryFrontierLoopBridge.lean
a47f9642deb9f233a5c6c8b00a18fdeec4e1dc272e3a1e506120fc5e8cea714b  proof/V7BinaryFrontierSortModel.lean
7ee9f9775b7b3e6f2d1ea8533e91b72cecbdb3948bdd5e3595c5ccc5e652fb66  proof/V7BinaryFrontierSortSourceBridge.lean
ec384cb07f8f830dd34791c46cbcbda0cd48d5f8581047a9637cf8a032bc7a38  proof/V7BinaryFrontierK13Integration.lean
562db62ed82b781748516ec5ffba155a5126922108f7251e9aa04e8c36baa78c  compile-generated.sh
2ec6131a1c77c21fbc92f36e718de75218337a767b31786eda6f7076e8ddd51d  caller/V7FirstCompact.llbc
1d7688f9495ace79397fe4265b11cd6be4be9fdf1ec38257211b2b2e558df190  caller/generated/V7FirstCompact/Funs.lean
69f6b6130cf9f72d574b96a3e5bf1304426f6d9fd9768dd80a75fbec8575eac4  caller/generated/V7FirstCompact/FunsExternal.lean
ad7c4abebd7f93332e65b97a858e36956ed79bfd75cf6630e88cfe31e5490d23  caller/generated/V7FirstCompact/Types.lean
9c573383d5b50dced1cd948f6886ac640cf03c375dacd0e8dfeabde699630aed  caller/generated/V7FirstCompact/TypesExternal.lean
f710b3691d4c4b6439386d8d456f90b37aec406ecbad3b0be8d76cf8f12e3f85  caller/generated/V7FirstCompact/translation.json
401c01f6295e20ba034480e95200b7acb860db9a00168c43e3a9cd13f9e637aa  caller/proof/V7FirstCompactFrontierBodyBridge.lean
b71fa9e8fc7bef1544ec981092de9370c4b45d4ed059f30989d7bef988932468  caller/proof/V7FirstCompactFrontierLoopBridge.lean
809eb566103b0a2355adaf530f78383dae45ac51d05ddf8fe4779b42b9e3a9bf  caller/proof/V7FirstCompactFrontierSortSourceBridge.lean
c72e3c80fcfd46ce032d834d00b209316608f2cb1b39840dbabdec8180e3aaa6  caller/proof/V7FirstCompactFrontierK13Integration.lean
38968fe0e71d83e4971bef2b26012fa7a52d1244b541564253d24db413eed85d  caller/proof/V7FirstCompactCallerBridge.lean
f21af0ef7f2362c62acb2dfa992c29d31f006aa5b13d788b64752b95d2f033bf  caller/proof/V7FirstCompactK13RawScheduleBridge.lean
6abb0376100611c5553258062480777187785579f402c9c1d3ce72379518258f  ../../crates/aspis-core/src/v7_onefold.rs
```

## Remaining source closure

The frontier mathematics, literal helper, caller-local helper, cap-203 semantic
equivalence, exact per-candidate schedule, translated first-success range loop,
and complete wrapper return are closed. The Aeneas early-return loss is removed
by the source refactor and fresh extraction. There is no remaining caller-local
frontier or first-selection control-flow premise.

The remaining system-level integration obligation is now the exact ordered
sampler-value alignment: for every scanned counter, show that the current
translated sampler's successful `Vec<u32>` is the first-unique 18-bit scan of
the same digest blocks already extracted by the accepted K1.3 evaluator and
scheduler router.  Array conversion, the `2^18` constant, frontier semantics,
cap selection, all five returned fields, and the outer first-success loop are
then theorem consequences rather than premises.
