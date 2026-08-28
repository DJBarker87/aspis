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

The next current-source checkpoint isolates the sole control-flow difference
between the older verified per-word sampler and the current Tag-73 extraction:
current Rust checked-adds the draw counter, while the older extraction lifted
wrapping addition.  `V7FirstCompactSamplerInnerBridge` proves that below the
literal 64-draw gate the checked increment cannot fail, increments exactly,
and equals the older wrapping value. It also proves the literal Rust mask
`0x3ffff` is exactly K1.3's `q16Candidate = word mod 2^18`, with no signedness
or codec premise. Focused unit `aspis-v7-q16-mask-01` exited 0 in 2.99 seconds,
peaked at 6,875,804 KiB RSS, and used zero swap. All three printed theorems
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Consequently the remaining sampler lemma is now precisely to replay the shared
per-word scan proof with Tag-73's `(count, bound, mask) = (16, 2^18,
2^18-1)`, using this checked-increment equivalence, and then compose it with
the already proved `raw_queries_eq_decoded_schedule`.  No additional Rust
sampler behavior remains unidentified.

That per-word replay is now kernel checked in
`V7FirstCompactSamplerLoop16Bridge.generated_inner_loop_matches_scanWords`.
It inducts over the literal current Aeneas `chunks_exact(4)` loop, proves exact
draw-before-decode ordering, little-endian decoding, 18-bit masking, first-only
duplicate handling, push order, count/draw stopping, and the labelled outer
marker for `(count, maxDraws) = (16, 64)`. The current checked increment is
rewritten through the preceding equivalence inside the proof. Focused unit
`aspis-v7-q16-loop16-03` exited 0 in 3.72 seconds, peaked at 6,897,860 KiB RSS,
and used zero swap; the theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`.

The same module now closes the byte-to-K1.3 seam for every squeeze block:
Aeneas four-byte decoding equals K1.3 `littleEndianWord`, the masked value is
exactly `q16Candidate`, and the literal `chunks_exact(4)` iterator yields the
eight K1.3 candidates in chronological order. Focused unit
`aspis-v7-q16-codec-final-01` exited 0 in 3.77 seconds, peaked at 6,920,272 KiB
RSS, used zero swap, and all four printed endpoints have the same standard
axiom set.

`V7FirstCompactSamplerOuterBridge` now adds the kernel-checked outer trace
foundation: it records only literal successful translated `squeeze_block`
calls, maps every returned block through the exact K1.3 byte/word/q16 codec,
proves trace and candidate-block append composition, and proves that each
literal `chunks_exact(4)` block satisfies the current inner-loop structural
premise. Focused unit `aspis-v7-q16-outer-trace-final-01` exited 0 in 2.72
seconds, peaked at 6,829,848 KiB RSS, and used zero swap. All three printed
endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The first recursive-wrapper attempt exposed a dependent-array proof-term
normalization seam between the current Aeneas `Array.to_slice` result and the
older imported `chunks_exact` equality. That seam is now closed by
`current_chunks_exact_block_is_blockChunks`, which re-elaborates the exact
equality in the current Tag-73 source environment rather than assuming it.
Focused unit `aspis-v7-q16-current-chunks-01` exited 0 in 9.25 seconds, peaked
at 6,912,424 KiB RSS, used zero swap, and reported only the standard axiom set.
The intentionally unclaimed next step remains the recursive translated-wrapper
composition using this current-local equality.

`V7FirstCompactSamplerNativeBlockBridge` closes the underlying dependent-array
type seam without coercing or assuming equality between separately elaborated
length proofs. It extracts the exact 32-byte block type from the translated
production transcript field, constructs its literal four-byte chunks, and
proves the resulting little-endian words, 18-bit q16 candidates, eight-word
candidate list, and iterator validity equal the K1.3 definitions. Focused NUC
unit `aspis-v7-q16-native-block-09` exited 0 in 2.92 seconds, peaked at
6,873,344 KiB RSS, and used zero swap. Every printed endpoint depends only on
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project axiom
is present. The same module now also proves that the literal translated
`Array.to_slice(...).chunks_exact(4)` operation returns this exact native
iterator, eliminating the remaining dependent-array conversion premise.
Focused unit `aspis-v7-q16-native-chunks-01` exited 0 in 9.16 seconds, peaked
at 6,931,784 KiB RSS, and used zero swap. Recursive outer-loop composition
remains the next unclaimed step.

The source-facing block boundary is now strengthened further: the semantic
codec uses a stable list-of-bytes subtype with an exact length-32 proof, while
`SourceSqueezeBlock` is extracted from the literal translated squeeze return.
`sourceSqueezeSlice_eq_nativeSourceSlice` proves byte-for-byte equality after
erasing only Aeneas' proof-carrying scalar witness, and
`sourceSqueeze_chunks_exact_is_nativeBlockChunks` proves the literal source
slice/chunks call returns the exact K1.3-connected iterator. Focused unit
`aspis-v7-q16-source-slice-01` exited 0 in 9.10 seconds, peaked at 6,942,216
KiB RSS, and used zero swap. Both endpoints report only `propext`,
`Classical.choice`, and `Quot.sound`. The remaining recursive body proof must
avoid unfolding the generated scalar witness at Lean's `instances`
transparency; no byte or sampler semantic premise remains at this seam.

`V7FirstCompactSamplerOuterBodyBridge` now removes that transparency seam
without patching generated Lean. It first lifts the exact source chunks
equality through the unchanged q16 continuation as a kernel congruence, then
proves `current_outer_body_eq_native`: the literal translated outer-loop body
is equal to the stable native refinement for every transcript, output vector,
and draw count. Focused unit `aspis-v7-q16-outer-congruence-02` exited 0 in
3.01 seconds, peaked at 6,835,488 KiB RSS, and used zero swap. Both printed
endpoints report only `propext`, `Classical.choice`, and `Quot.sound`. The next
step is the recursive WP composition over this now-exact body equality. The
same module now proves `current_outer_loop_eq_native`, lifting that body
equality through Aeneas' complete recursive `loop` and replacing the literal
translated q16 outer loop with the stable native refinement. Focused NUC unit
`aspis-v7-q16-outer-loop-03` exited 0 in 2.98 seconds, peaked at 6,831,428 KiB
RSS, and used zero swap. The new endpoint again reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.

`V7FirstCompactSamplerOuterLoopBridge` now proves the recursive operational
step as well. `generated_outer_loop_matches_scanBlocks` starts from the literal
translated q16 outer loop, records the exact successful source squeeze trace,
and proves that every returned vector and draw count implements the fixed
K1.3 `scanBlocks 16 64` model in chronological word order. Its only explicit
operational premise is that the source squeeze calls used by this total-WP run
succeed; no byte-codec or sampler-semantics equality is assumed. Focused NUC
unit `aspis-v7-q16-outer-wp-02` exited 0 in 3.32 seconds, peaked at 6,879,120
KiB RSS, and used zero swap. The endpoint reports exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or project axiom.

`V7FirstCompactSamplerWrapperBridge` closes the public sampler/caller seam.
It proves the exact fixed-call arithmetic for `(count,bound,max_draws) =
(16,2^18,64)`, inverts successful translated wrapper execution to the literal
recursive loop run, then obtains that run directly from `RawCandidateExecution`
and composes it with the chronological K1.3 block-scan postcondition. Focused
NUC unit `aspis-v7-q16-wrapper-08` exited 0 in 2.91 seconds, peaked at
6,865,028 KiB RSS, and used zero swap. All three source endpoints report
exactly `propext`, `Classical.choice`, and `Quot.sound`.

`V7FirstCompactSamplerK13PositionBridge` closes the remaining deterministic
sampler mathematics. It proves that the exact source squeeze trace flattens to
the chronological K1.3 digest words, that a successful `scanBlocks 16 64`
result equals `scanQ16` on those digests, and that the raw production
candidate's sampled vector is exactly that ordered position list. Focused NUC
unit `aspis-v7-q16-k13-position-03` exited 0 in 2.82 seconds, peaked at
6,868,440 KiB RSS, and used zero swap. All endpoints report subsets of
`propext`, `Classical.choice`, and `Quot.sound`.

`V7FirstCompactSqueezeSourceBridge` makes the remaining SHA boundary exact at
literal source level. It proves that current `squeeze_block` hashes precisely
the 33-byte inputs `state || 1` and `state || 2`, that totality of the specific
installed callback implies squeeze success, and that successful squeezing
preserves that callback. Focused NUC unit
`aspis-v7-q16-squeeze-source-01` exited 0 in 3.41 seconds, peaked at
6,865,936 KiB RSS, and used zero swap. All endpoints report exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The recursive outer-loop, wrapper, and K1.3 position bridges now use that exact
source boundary directly: their only operational premise is totality of the
callback installed in the accepted transcript.  The loop invariant proves the
same callback is preserved across every squeeze, eliminating the former global
premise over arbitrary transcripts. Focused NUC unit
`aspis-v7-q16-callback-thread-06` exited 0; the final target took 2.83 seconds,
peaked at 6,875,636 KiB RSS, and used zero swap. All endpoints report subsets
of `propext`, `Classical.choice`, and `Quot.sound`.

`V7FirstCompactSamplerTableTraceBridge` closes the deterministic fixed-table
part of the source/scheduler seam. A table-aligned literal translated squeeze
trace is proved to return exactly the semantic Tag-73 duplex blocks and final
digest, and forgetting table alignment recovers the existing source trace. Its
`SourceSqueezeRuntimeReflection` is the minimal effectful boundary: recursively
it contains only the two exact table lookups corresponding to each already
proved successful translated callback pair, and kernel code constructs the
table-aligned trace from it.
Focused NUC unit `aspis-v7-q16-table-trace-05` exited 0 in 2.78 seconds, peaked
at 6,843,764 KiB RSS, and used zero swap. Its endpoints report subsets of
`propext`, `Classical.choice`, and `Quot.sound`.

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
128ac3fb23f46ae234b6472c78c27b938b458933d102cdc9be1c5cab8dbb85f4  caller/proof/V7FirstCompactSamplerInnerBridge.lean
38a125601298e71ccb2c28f16a9ab222ce377f606f24e3ddfd84b30c040d0e20  caller/proof/V7FirstCompactSamplerLoop16Bridge.lean
92accefcb0d123584e5007b45427eb44c6e31ad65e314a0b1c3d76e0d5cfbea5  caller/proof/V7FirstCompactSamplerOuterBridge.lean
6da8875b86b2b2b912a1736408bdca6d22cd74187f9b2670de9edb0199cd8d75  caller/proof/V7FirstCompactSamplerNativeBlockBridge.lean
9a0f680b6e93be014c37f7a5bc5be2454262bbb9eaedec5a8c1104436f5d8516  caller/proof/V7FirstCompactSamplerOuterBodyBridge.lean
d71bbd19f44d407846820acb8bbe167f953925d819ef0313bf2e591cd1a7d888  caller/proof/V7FirstCompactSamplerOuterLoopBridge.lean
5a1f6a37166be553c5305d31ce097c884aabed56b0a1820d91c8f98f03e0ed63  caller/proof/V7FirstCompactSamplerWrapperBridge.lean
5ea4cdf362d9db303aeb1d510ab9c0a47ce48dfc9956f5b462e6c1c0d39ad222  caller/proof/V7FirstCompactSamplerK13PositionBridge.lean
0caaeb316b41ff595566a4eba00a4c13c1ee98ed7e6f55936e7e5765e0c5045e  caller/proof/V7FirstCompactSqueezeSourceBridge.lean
7328ec04446908cf5eddf3a709b7893f02687275e70c911cf75fb0fcf4a8c877  caller/proof/V7FirstCompactSamplerTableTraceBridge.lean
6abb0376100611c5553258062480777187785579f402c9c1d3ce72379518258f  ../../crates/aspis-core/src/v7_onefold.rs
```

## Remaining source closure

The frontier mathematics, literal helper, caller-local helper, cap-203 semantic
equivalence, exact per-candidate schedule, translated first-success range loop,
and complete wrapper return are closed. The Aeneas early-return loss is removed
by the source refactor and fresh extraction. There is no remaining caller-local
frontier or first-selection control-flow premise.

The recursive proof now uses totality of only the installed production hash
callback, and the deterministic source trace is connected to the fixed-table
semantic duplex. The remaining system-level obligation is operational lookup
provenance: show that every actual callback result in the accepted translated
trace is the corresponding entry in the exact scheduler table. The semantic
decoder result and `raw_queries_eq_decoded_schedule` then close the ordered
array. Array conversion, the `2^18` constant, frontier semantics, cap selection,
all five returned fields, and the outer first-success loop are theorem
consequences rather than premises.
